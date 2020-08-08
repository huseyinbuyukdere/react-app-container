/// <reference types="react" />
import { ContainerRoute, DesignConfig } from './models';
interface ContainerProps {
    children: any;
    selectedRoute?: ContainerRoute;
    routes?: ContainerRoute[];
    designConfig?: DesignConfig;
}
declare const Container: (props: ContainerProps) => JSX.Element;
export default Container;
